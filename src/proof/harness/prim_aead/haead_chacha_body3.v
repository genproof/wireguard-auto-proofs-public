(* law prim_aead: the reference ChaCha20 / HChaCha20 of common.h. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require Import WgNoise.proof.harness.prim_aead.haead_lemmas3.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Lemma hcc3_rotl_eq x n : 0 < n < 32 ->
  Int.or (Int.shl x (Int.repr n)) (Int.shru x (Int.repr (32 - n))) = Int.rol x (Int.repr n).
Proof.
  intros Hn.
  assert (L: forall k, 0 <= k < 32 -> Int.ltu (Int.repr k) Int.iwordsize = true).
  { intros k Hk. unfold Int.ltu. rewrite Int.unsigned_repr by rep_lia. change (Int.unsigned Int.iwordsize) with 32. destruct (zlt k 32); auto; lia. }
  rewrite <- Int.or_ror; [ | apply L; lia | apply L; lia | ].
  - rewrite Int.ror_rol by (apply L; lia). f_equal. unfold Int.sub.
    change (Int.unsigned Int.iwordsize) with 32. rewrite Int.unsigned_repr by rep_lia. f_equal; lia.
  - unfold Int.add. rewrite !Int.unsigned_repr by rep_lia. replace (n + (32 - n)) with 32 by lia. reflexivity.
Qed.

Lemma hcc3_rotl_body :
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rc_rotl rc_rotl_spec.
Proof.
  start_function.
  forward.
  - entailer!. change (Int.unsigned Int.iwordsize) with 32. lia.
  - entailer!. rewrite hcc3_rotl_eq by lia. reflexivity.
Qed.

(* the quarter round as 8 steps (same order as the C) *)
Definition hcc3_sa (i j: Z) (x: list int) : list int := upd_Znth i x (Int.add (Znth i x) (Znth j x)).
Definition hcc3_sr (i j r: Z) (x: list int) : list int :=
  upd_Znth i x (Int.rol (Int.xor (Znth i x) (Znth j x)) (Int.repr r)).

Lemma hcc3_qround_eq x a b c d : chacha_qround x a b c d =
  hcc3_sr b c 7 (hcc3_sa c d (hcc3_sr d a 8 (hcc3_sa a b
    (hcc3_sr b c 12 (hcc3_sa c d (hcc3_sr d a 16 (hcc3_sa a b x))))))).
Proof. unfold chacha_qround, hcc3_sr, hcc3_sa. cbv zeta. reflexivity. Qed.

Lemma hcc3_sa_len i j x : 0 <= i < Zlength x -> Zlength (hcc3_sa i j x) = Zlength x.
Proof. intros. unfold hcc3_sa. rewrite upd_Znth_Zlength; lia. Qed.
Lemma hcc3_sr_len i j r x : 0 <= i < Zlength x -> Zlength (hcc3_sr i j r x) = Zlength x.
Proof. intros. unfold hcc3_sr. rewrite upd_Znth_Zlength; lia. Qed.

Ltac hcc3_sa_step i j xk xn En Ln :=
  forward; forward; forward; rewrite upd_Znth_map;
  change (upd_Znth i xk (Int.add (Znth i xk) (Znth j xk))) with (hcc3_sa i j xk);
  assert (Ln: Zlength (hcc3_sa i j xk) = 16) by (rewrite hcc3_sa_len; lia);
  remember (hcc3_sa i j xk) as xn eqn:En; try deadvars!.

Ltac hcc3_sr_step i j r xk xn En Ln :=
  forward; forward; forward_call (Int.xor (Znth i xk) (Znth j xk), r); forward; rewrite upd_Znth_map;
  change (upd_Znth i xk (Int.rol (Int.xor (Znth i xk) (Znth j xk)) (Int.repr r))) with (hcc3_sr i j r xk);
  assert (Ln: Zlength (hcc3_sr i j r xk) = 16) by (rewrite hcc3_sr_len; lia);
  remember (hcc3_sr i j r xk) as xn eqn:En; try deadvars!.

Lemma hcc3_qr_body :
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rc_qr rc_qr_spec.
Proof.
  start_function.
  hcc3_sa_step a b x x1 E1 L1.
  hcc3_sr_step d a 16 x1 x2 E2 L2.
  hcc3_sa_step c d x2 x3 E3 L3.
  hcc3_sr_step b c 12 x3 x4 E4 L4.
  hcc3_sa_step a b x4 x5 E5 L5.
  hcc3_sr_step d a 8 x5 x6 E6 L6.
  hcc3_sa_step c d x6 x7 E7 L7.
  hcc3_sr_step b c 7 x7 x8 E8 L8.
  rewrite hcc3_qround_eq. subst x1 x2 x3 x4 x5 x6 x7 x8. entailer!.
Qed.

Lemma hcc3_qround_len x a b c d : Zlength x = 16 -> 0 <= a < 16 -> 0 <= b < 16 -> 0 <= c < 16 -> 0 <= d < 16 ->
  Zlength (chacha_qround x a b c d) = 16.
Proof.
  intros. rewrite hcc3_qround_eq.
  repeat first [rewrite hcc3_sa_len | rewrite hcc3_sr_len]; auto; lia.
Qed.

Lemma hcc3_dround_eq x : chacha_dround x =
  chacha_qround (chacha_qround (chacha_qround (chacha_qround (chacha_qround (chacha_qround (chacha_qround
    (chacha_qround x 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15) 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14.
Proof. unfold chacha_dround. cbv zeta. reflexivity. Qed.

Lemma hcc3_dround_len x : Zlength x = 16 -> Zlength (chacha_dround x) = 16.
Proof. intros. rewrite hcc3_dround_eq. repeat (apply hcc3_qround_len; try lia). Qed.

Lemma hcc3_rounds_S1 n x : chacha_rounds (S n) x = chacha_rounds n (chacha_dround x).
Proof. unfold chacha_rounds. reflexivity. Qed.

Lemma hcc3_rounds_S n x : chacha_rounds (S n) x = chacha_dround (chacha_rounds n x).
Proof.
  revert x. induction n; intros x.
  - rewrite hcc3_rounds_S1. reflexivity.
  - rewrite hcc3_rounds_S1. rewrite IHn. rewrite <- hcc3_rounds_S1. reflexivity.
Qed.

Lemma hcc3_rounds_len n x : Zlength x = 16 -> Zlength (chacha_rounds n x) = 16.
Proof.
  revert x. induction n; intros x Hx; [exact Hx |].
  rewrite hcc3_rounds_S1. apply IHn. apply hcc3_dround_len; auto.
Qed.

Module HC3.
  Definition _x := WgNoise.harness.x_prim_aead.code._x.
  Definition _i := WgNoise.harness.x_prim_aead.code._i.
  Definition _rc_qr := WgNoise.harness.x_prim_aead.code._rc_qr.
End HC3.

(* one call of rc_qr in rc_rounds (a separate lemma: two forward_calls in one proof gave a Qed over 600 s) *)
Lemma hcc3_rounds_call {Espec: OracleKind} sh xp (i: Z) (y: list int) (a b c d: Z) :
  writable_share sh -> Zlength y = 16 -> 0 <= a < 16 -> 0 <= b < 16 -> 0 <= c < 16 -> 0 <= d < 16 ->
  semax (func_tycontext WgNoise.harness.x_prim_aead.code.f_rc_rounds haead_V haead_Gprog nil)
    (PROP () LOCAL (temp HC3._i (Vint (Int.repr i)); temp HC3._x xp)
     SEP (data_at sh (tarray tuint 16) (map Vint y) xp))
    (Scall None (Evar HC3._rc_qr (Tfunction ((tptr tuint) :: tint :: tint :: tint :: tint :: nil) tvoid cc_default))
      ((Etempvar HC3._x (tptr tuint)) :: (Econst_int (Int.repr a) tint) :: (Econst_int (Int.repr b) tint) ::
       (Econst_int (Int.repr c) tint) :: (Econst_int (Int.repr d) tint) :: nil))
    (normal_ret_assert (PROP () LOCAL (temp HC3._i (Vint (Int.repr i)); temp HC3._x xp)
     SEP (data_at sh (tarray tuint 16) (map Vint (chacha_qround y a b c d)) xp))).
Proof.
  intros. abbreviate_semax. forward_call (sh, xp, y, a, b, c, d). entailer!.
Qed.

Ltac hcc3_rcall yk yn En Ln :=
  try match goal with M := @abbreviate statement _ |- _ => unfold M, abbreviate; clear M end;
  eapply semax_seq'; [apply hcc3_rounds_call; auto; lia | ];
  match goal with |- context [chacha_qround yk ?a ?b ?c ?d] =>
    assert (Ln: Zlength (chacha_qround yk a b c d) = 16) by (apply hcc3_qround_len; auto; lia);
    remember (chacha_qround yk a b c d) as yn eqn:En end.

Lemma hcc3_rounds_body :
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rc_rounds rc_rounds_spec.
Proof.
  start_function.
  forward_for_simple_bound 10 (EX i: Z,
    PROP () LOCAL (temp WgNoise.harness.x_prim_aead.code._x xp)
    SEP (data_at sh (tarray tuint 16) (map Vint (chacha_rounds (Z.to_nat i) x)) xp))%assert.
  - entailer!.
  - assert (L0: Zlength (chacha_rounds (Z.to_nat i) x) = 16) by (apply hcc3_rounds_len; auto).
    remember (chacha_rounds (Z.to_nat i) x) as y0 eqn:E0.
    hcc3_rcall y0 y1 E1 L1. hcc3_rcall y1 y2 E2 L2. hcc3_rcall y2 y3 E3 L3. hcc3_rcall y3 y4 E4 L4.
    hcc3_rcall y4 y5 E5 L5. hcc3_rcall y5 y6 E6 L6. hcc3_rcall y6 y7 E7 L7.
    eapply semax_post; cycle 4; [apply hcc3_rounds_call; auto; lia | ..];
      unfold POSTCONDITION, abbreviate; simpl_ret_assert; try (normalize; fail).
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    rewrite hcc3_rounds_S, hcc3_dround_eq, <- E0, <- E1, <- E2, <- E3, <- E4, <- E5, <- E6, <- E7.
    generalize (chacha_qround y7 3 4 9 14); intros y8. clear E0 E1 E2 E3 E4 E5 E6 E7. entailer!.
  - change (Z.to_nat 10) with 10%nat. remember (chacha_rounds 10 x) as r. clear Heqr. entailer!.
Qed.

Lemma hcc3_le32_words_len n bs : Zlength (le32_words n bs) = Z.of_nat n.
Proof. unfold le32_words. rewrite !Zlength_map, Zlength_correct, seq_length. reflexivity. Qed.

Lemma hcc3_le32_words_nth n bs i : 0 <= i < Z.of_nat n -> Znth i (le32_words n bs) = le32_at bs (4 * i).
Proof.
  intros Hi. unfold le32_words. rewrite Znth_map by (rewrite Zlength_map, Zlength_correct, seq_length; lia).
  rewrite Znth_map by (rewrite Zlength_correct, seq_length; lia).
  rewrite <- nth_Znth by (rewrite Zlength_correct, seq_length; lia).
  rewrite seq_nth by lia. f_equal. f_equal. lia.
Qed.

Lemma hcc3_setup_step (key: list byte) (i: Z) : 0 <= i < 8 ->
  upd_Znth (4 + i) (map Vint chacha_consts ++ map Vint (sublist 0 i (le32_words 8 key)) ++ Zrepeat Vundef (12 - i))
    (Vint (le32_at key (4 * i))) =
  map Vint chacha_consts ++ map Vint (sublist 0 (i + 1) (le32_words 8 key)) ++ Zrepeat Vundef (12 - (i + 1)).
Proof.
  intros Hi. pose proof (hcc3_le32_words_len 8 key). pose proof (hcc3_le32_words_nth 8 key i ltac:(lia)).
  rewrite (sublist_split 0 i (i + 1)) by (simpl in *; lia). rewrite (sublist_one i (i + 1)) by (simpl in *; lia).
  rewrite H0. unfold chacha_consts. list_solve.
Qed.

Lemma hcc3_setup_body :
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rc_setup rc_setup_spec.
Proof.
  start_function.
  forward. forward. forward. forward.
  forward_for_simple_bound 8 (EX i: Z,
    PROP () LOCAL (temp WgNoise.harness.x_prim_aead.code._s sp; temp WgNoise.harness.x_prim_aead.code._key kp;
      temp WgNoise.harness.x_prim_aead.code._w12 (Vint w12); temp WgNoise.harness.x_prim_aead.code._w13 (Vint w13);
      temp WgNoise.harness.x_prim_aead.code._w14 (Vint w14); temp WgNoise.harness.x_prim_aead.code._w15 (Vint w15))
    SEP (data_at sh (tarray tuint 16)
           (map Vint chacha_consts ++ map Vint (sublist 0 i (le32_words 8 key)) ++ Zrepeat Vundef (12 - i)) sp;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp))%assert.
  - entailer!.
  - forward_call (ksh, kp, 4 * i, key). { entailer!. } { rewrite H. cancel. }
    rewrite H. forward. rewrite hcc3_setup_step by lia. entailer!.
  - forward. forward. forward. forward. entailer!.
Qed.

Lemma hcc3_lo n : 0 <= n <= Int64.max_unsigned -> Int.repr (Int64.unsigned (Int64.repr n)) = Int.repr n.
Proof. intros. rewrite Int64.unsigned_repr by lia. reflexivity. Qed.

Lemma hcc3_hi n : 0 <= n <= Int64.max_unsigned ->
  Int.repr (Int64.unsigned (Int64.shru (Int64.repr n) (Int64.repr 32))) = Int.repr (Z.shiftr n 32).
Proof.
  intros. unfold Int64.shru. rewrite (Int64.unsigned_repr n) by lia. change (Int64.unsigned (Int64.repr 32)) with 32.
  rewrite Int64.unsigned_repr; [reflexivity |].
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia |].
  apply Z.le_trans with n; [apply Z.div_le_upper_bound; lia | lia].
Qed.

Lemma hcc3_words_bytes_len l : Zlength (words_bytes l) = 4 * Zlength l.
Proof.
  induction l; [reflexivity |]. change (words_bytes (a :: l)) with (le32_bytes a ++ words_bytes l).
  rewrite Zlength_app, IHl, Zlength_cons. change (Zlength (le32_bytes a)) with 4. lia.
Qed.

Lemma hcc3_words_bytes_app a b : words_bytes (a ++ b) = words_bytes a ++ words_bytes b.
Proof. unfold words_bytes. rewrite map_app, concat_app. reflexivity. Qed.

Lemma hcc3_words_bytes_snoc W i : 0 <= i < Zlength W ->
  words_bytes (sublist 0 (i + 1) W) = words_bytes (sublist 0 i W) ++ le32_bytes (Znth i W).
Proof.
  intros. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite (sublist_one i (i + 1) W) by lia.
  rewrite hcc3_words_bytes_app. change (words_bytes [Znth i W]) with (le32_bytes (Znth i W) ++ []). rewrite app_nil_r. reflexivity.
Qed.

Lemma hcc3_splice (a: list val) (w: int) (k: Z) (b: list val) : 4 <= k ->
  haead_splice (Zlength a) (le32_bytes w) (a ++ Zrepeat Vundef k ++ b) =
  (a ++ map Vubyte (le32_bytes w)) ++ Zrepeat Vundef (k - 4) ++ b.
Proof.
  intros Hk. unfold haead_splice. assert (Zlength (le32_bytes w) = 4) by reflexivity.
  rewrite H. list_solve.
Qed.

Lemma hcc3_add_words_nth a b i : Zlength a = Zlength b -> 0 <= i < Zlength a ->
  Znth i (add_words a b) = Int.add (Znth i a) (Znth i b).
Proof.
  intros. unfold add_words. rewrite Znth_map by (rewrite Zlength_combine; lia).
  rewrite Znth_combine by auto. reflexivity.
Qed.

Lemma hcc3_add_words_len a b : Zlength a = Zlength b -> Zlength (add_words a b) = Zlength a.
Proof. intros. unfold add_words. rewrite Zlength_map, Zlength_combine. lia. Qed.

Lemma hcc3_store_step_gen (p: list val) (W: list int) (i: Z) (b: list val) :
  0 <= i < Zlength W ->
  haead_splice (Zlength p + 4 * i) (le32_bytes (Znth i W))
    (p ++ map Vubyte (words_bytes (sublist 0 i W)) ++ Zrepeat Vundef (4 * Zlength W - 4 * i) ++ b) =
  p ++ map Vubyte (words_bytes (sublist 0 (i + 1) W)) ++ Zrepeat Vundef (4 * Zlength W - 4 * (i + 1)) ++ b.
Proof.
  intros.
  assert (Hl: Zlength (p ++ map Vubyte (words_bytes (sublist 0 i W))) = Zlength p + 4 * i)
    by (rewrite Zlength_app, Zlength_map, hcc3_words_bytes_len, Zlength_sublist by lia; lia).
  pose proof (hcc3_splice (p ++ map Vubyte (words_bytes (sublist 0 i W))) (Znth i W) (4 * Zlength W - 4 * i) b
    ltac:(lia)) as HS.
  rewrite Hl, <- !app_assoc in HS. rewrite HS.
  rewrite hcc3_words_bytes_snoc by lia. rewrite map_app, <- !app_assoc.
  replace (4 * Zlength W - 4 * (i + 1)) with (4 * Zlength W - 4 * i - 4) by lia. reflexivity.
Qed.

Lemma hcc3_store_step (W: list int) (i: Z) (b: list val) :
  0 <= i < Zlength W ->
  haead_splice (4 * i) (le32_bytes (Znth i W))
    (map Vubyte (words_bytes (sublist 0 i W)) ++ Zrepeat Vundef (4 * Zlength W - 4 * i) ++ b) =
  map Vubyte (words_bytes (sublist 0 (i + 1) W)) ++ Zrepeat Vundef (4 * Zlength W - 4 * (i + 1)) ++ b.
Proof. intros. apply (hcc3_store_step_gen [] W i b H). Qed.

Module HB3.
  Definition _x := WgNoise.harness.x_prim_aead.code._x.
  Definition _s := WgNoise.harness.x_prim_aead.code._s.
  Definition _i := WgNoise.harness.x_prim_aead.code._i.
  Definition _out := WgNoise.harness.x_prim_aead.code._out.
  Definition _key := WgNoise.harness.x_prim_aead.code._key.
  Definition _ctr := WgNoise.harness.x_prim_aead.code._ctr.
  Definition _n := WgNoise.harness.x_prim_aead.code._n.
  Definition _rc_rounds := WgNoise.harness.x_prim_aead.code._rc_rounds.
End HB3.

(* the rc_rounds call of ref_chacha20_block, in its own lemma (see hcc3_rounds_call) *)
Lemma hcc3_block_rounds_call {Espec: OracleKind} (st: list int) v_x v_s out kp ctr n (A B C: mpred) :
  Zlength st = 16 ->
  semax (func_tycontext WgNoise.harness.x_prim_aead.code.f_ref_chacha20_block haead_V haead_Gprog nil)
    (PROP () LOCAL (temp HB3._i (Vint (Int.repr 16)); lvar HB3._x (tarray tuint 16) v_x;
      lvar HB3._s (tarray tuint 16) v_s; temp HB3._out out; temp HB3._key kp;
      temp HB3._ctr (Vint ctr); temp HB3._n (Vlong (Int64.repr n)))
     SEP (A; B; data_at Tsh (tarray tuint 16) (map Vint st) v_x; C))
    (Scall None (Evar HB3._rc_rounds (Tfunction ((tptr tuint) :: nil) tvoid cc_default))
      ((Evar HB3._x (tarray tuint 16)) :: nil))
    (normal_ret_assert (PROP () LOCAL (temp HB3._i (Vint (Int.repr 16)); lvar HB3._x (tarray tuint 16) v_x;
      lvar HB3._s (tarray tuint 16) v_s; temp HB3._out out; temp HB3._key kp;
      temp HB3._ctr (Vint ctr); temp HB3._n (Vlong (Int64.repr n)))
     SEP (A; B; data_at Tsh (tarray tuint 16) (map Vint (chacha_rounds 10 st)) v_x; C))).
Proof.
  intros. abbreviate_semax. forward_call (Tsh, v_x, st). generalize (chacha_rounds 10 st); intros r. entailer!.
Qed.

Local Opaque Int64.shru.

Lemma hcc3_block_body : haead_hyps ->
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_ref_chacha20_block ref_chacha20_block_spec.
Proof.
  intros HH. destruct HH as (_ & (HST & _) & _).
  start_function.
  pose proof (HST key n ctr H H0) as Est.
  remember (Int64.repr n) as nn eqn:En.
  forward_call (Tsh, v_s, ksh, kp, key, ctr, Int.zero, Int.repr (Int64.unsigned nn),
    Int.repr (Int64.unsigned (Int64.shru nn (Int64.repr 32)))).
  subst nn. rewrite hcc3_lo, hcc3_hi, Est by lia.
  assert (Lst: Zlength (chacha_advance (aead_st key n) (Int.unsigned ctr)) = 16).
  { rewrite <- Est. unfold chacha_consts. rewrite !Zlength_app, hcc3_le32_words_len. reflexivity. }
  remember (chacha_advance (aead_st key n) (Int.unsigned ctr)) as st eqn:Est'. clear Est HST.
  forward_for_simple_bound 16 (EX i: Z,
    PROP () LOCAL (lvar WgNoise.harness.x_prim_aead.code._x (tarray tuint 16) v_x;
      lvar WgNoise.harness.x_prim_aead.code._s (tarray tuint 16) v_s;
      temp WgNoise.harness.x_prim_aead.code._out out; temp WgNoise.harness.x_prim_aead.code._key kp;
      temp WgNoise.harness.x_prim_aead.code._ctr (Vint ctr); temp WgNoise.harness.x_prim_aead.code._n (Vlong (Int64.repr n)))
    SEP (data_at Tsh (tarray tuint 16) (map Vint st) v_s; data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
         data_at Tsh (tarray tuint 16) (map Vint (sublist 0 i st) ++ Zrepeat Vundef (16 - i)) v_x;
         data_at_ osh (tarray tuchar 64) out))%assert.
  - entailer!.
  - forward. forward. entailer!. list_solve.
  - replace (map Vint (sublist 0 16 st) ++ Zrepeat Vundef (16 - 16)) with (map Vint st) by list_solve.
    eapply semax_seq'; [apply hcc3_block_rounds_call; auto | ].
    assert (Lr: Zlength (chacha_rounds 10 st) = 16) by (apply hcc3_rounds_len; auto).
    remember (chacha_rounds 10 st) as r eqn:Er.
    assert (EW: chacha_block_bytes 10 st = words_bytes (add_words r st))
      by (subst r; unfold chacha_block_bytes, chacha_block_words; reflexivity).
    clear Er Est'.
    assert (LW: Zlength (add_words r st) = 16) by (rewrite hcc3_add_words_len; lia).
    remember (add_words r st) as W eqn:EW0.
    unfold MORE_COMMANDS, abbreviate.
    forward_for_simple_bound 16 (EX i: Z,
      PROP () LOCAL (lvar WgNoise.harness.x_prim_aead.code._x (tarray tuint 16) v_x;
        lvar WgNoise.harness.x_prim_aead.code._s (tarray tuint 16) v_s;
        temp WgNoise.harness.x_prim_aead.code._out out)
      SEP (data_at Tsh (tarray tuint 16) (map Vint st) v_s; data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
           data_at Tsh (tarray tuint 16) (map Vint r) v_x;
           data_at osh (tarray tuchar 64) (map Vubyte (words_bytes (sublist 0 i W)) ++ Zrepeat Vundef (64 - 4 * i) ++ []) out))%assert.
    + entailer!.
    + forward. forward.
      assert (EWi: Int.add (Znth i r) (Znth i st) = Znth i W) by (subst W; rewrite hcc3_add_words_nth; auto; lia).
      assert (Lc: Zlength (map Vubyte (words_bytes (sublist 0 i W)) ++ Zrepeat Vundef (64 - 4 * i) ++ []) = 64).
      { rewrite !Zlength_app, Zlength_map, hcc3_words_bytes_len, Zlength_sublist, Zlength_Zrepeat by lia.
        rewrite Zlength_nil. lia. }
      forward_call (osh, out, 4 * i, map Vubyte (words_bytes (sublist 0 i W)) ++ Zrepeat Vundef (64 - 4 * i) ++ [],
        Znth i W).
      { entailer!. rewrite EWi. reflexivity. }
      { rewrite Lc. cancel. }
      pose proof (hcc3_store_step W i [] ltac:(lia)) as HSt.
      replace (4 * Zlength W) with 64 in HSt by lia.
      rewrite Lc, HSt. entailer!.
    + rewrite EW, sublist_same by lia. change (64 - 4 * 16) with 0. rewrite Zrepeat_0, !app_nil_r.
      clear EW EW0. entailer!.
Qed.

Lemma hcc3_init_eq (key nb: list byte) : 16 <= Zlength nb ->
  chacha_consts ++ le32_words 8 key ++ [le32_at nb 0; le32_at nb 4; le32_at nb 8; le32_at nb 12] =
  chacha_init_st (le32_words 8 key) (sublist 0 16 nb).
Proof.
  intros. unfold chacha_init_st, le32_at. rewrite !Znth_sublist by lia. reflexivity.
Qed.

Module HH3.
  Definition _nonce16 := WgNoise.harness.x_prim_aead.code._nonce16.
End HH3.

(* the rc_rounds call of ref_hchacha20, in its own lemma (see hcc3_rounds_call) *)
Lemma hcc3_hch_rounds_call {Espec: OracleKind} (st: list int) v_x out (A B C: mpred) :
  Zlength st = 16 ->
  semax (func_tycontext WgNoise.harness.x_prim_aead.code.f_ref_hchacha20 haead_V haead_Gprog nil)
    (PROP () LOCAL (lvar HB3._x (tarray tuint 16) v_x; temp HB3._out out)
     SEP (data_at Tsh (tarray tuint 16) (map Vint st) v_x; A; B; C))
    (Scall None (Evar HB3._rc_rounds (Tfunction ((tptr tuint) :: nil) tvoid cc_default))
      ((Evar HB3._x (tarray tuint 16)) :: nil))
    (normal_ret_assert (PROP () LOCAL (lvar HB3._x (tarray tuint 16) v_x; temp HB3._out out)
     SEP (data_at Tsh (tarray tuint 16) (map Vint (chacha_rounds 10 st)) v_x; A; B; C))).
Proof.
  intros. abbreviate_semax. forward_call (Tsh, v_x, st). generalize (chacha_rounds 10 st); intros r. entailer!.
Qed.

Lemma hcc3_hchacha_body : haead_hyps ->
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_ref_hchacha20 ref_hchacha20_spec.
Proof.
  intros _.
  start_function.
  forward_call (nsh, np, 0, nb). { entailer!. }
  forward_call (nsh, np, 4, nb). { entailer!. }
  forward_call (nsh, np, 8, nb). { entailer!. }
  forward_call (nsh, np, 12, nb). { entailer!. }
  forward_call (Tsh, v_x, ksh, kp, key, le32_at nb 0, le32_at nb 4, le32_at nb 8, le32_at nb 12).
  rewrite hcc3_init_eq by lia.
  assert (Lst: Zlength (chacha_init_st (le32_words 8 key) (sublist 0 16 nb)) = 16).
  { unfold chacha_init_st, chacha_consts. rewrite !Zlength_app, hcc3_le32_words_len. reflexivity. }
  remember (chacha_init_st (le32_words 8 key) (sublist 0 16 nb)) as st eqn:Est.
  deadvars!.
  eapply semax_seq'; [apply hcc3_hch_rounds_call; auto | ].
  assert (LR: Zlength (chacha_rounds 10 st) = 16) by (apply hcc3_rounds_len; auto).
  remember (chacha_rounds 10 st) as R eqn:ER.
  assert (EH: hchacha_words 10 st = sublist 0 4 R ++ sublist 12 16 R)
    by (subst R; unfold hchacha_words; cbv zeta; reflexivity).
  clear ER Est.
  assert (LA: Zlength (sublist 0 4 R) = 4) by (rewrite Zlength_sublist; lia).
  assert (LB: Zlength (sublist 12 16 R) = 4) by (rewrite Zlength_sublist; lia).
  assert (NA: forall i, 0 <= i < 4 -> Znth i (sublist 0 4 R) = Znth i R)
    by (intros; rewrite Znth_sublist by lia; f_equal; lia).
  assert (NB: forall i, 0 <= i < 4 -> Znth i (sublist 12 16 R) = Znth (12 + i) R)
    by (intros; rewrite Znth_sublist by lia; f_equal; lia).
  remember (sublist 0 4 R) as A eqn:EA. remember (sublist 12 16 R) as B eqn:EB.
  unfold MORE_COMMANDS, abbreviate.
  forward_for_simple_bound 4 (EX i: Z,
    PROP () LOCAL (lvar WgNoise.harness.x_prim_aead.code._x (tarray tuint 16) v_x;
      temp WgNoise.harness.x_prim_aead.code._out out)
    SEP (data_at Tsh (tarray tuint 16) (map Vint R) v_x; data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
         data_at nsh (tarray tuchar (Zlength nb)) (map Vubyte nb) np;
         data_at osh (tarray tuchar 32) (map Vubyte (words_bytes (sublist 0 i A)) ++ Zrepeat Vundef (16 - 4 * i) ++
           map Vubyte (words_bytes (sublist 0 i B)) ++ Zrepeat Vundef (16 - 4 * i) ++ []) out))%assert.
  - entailer!.
  - forward.
    set (bB := map Vubyte (words_bytes (sublist 0 i B)) ++ Zrepeat Vundef (16 - 4 * i) ++ []).
    assert (Lc: Zlength (map Vubyte (words_bytes (sublist 0 i A)) ++ Zrepeat Vundef (16 - 4 * i) ++ bB) = 32).
    { unfold bB. rewrite !Zlength_app, !Zlength_map, !hcc3_words_bytes_len, !Zlength_sublist, Zlength_Zrepeat,
        Zlength_nil by lia. lia. }
    forward_call (osh, out, 4 * i, map Vubyte (words_bytes (sublist 0 i A)) ++ Zrepeat Vundef (16 - 4 * i) ++ bB,
      Znth i A).
    { entailer!. rewrite NA by lia. reflexivity. }
    { rewrite Lc. cancel. }
    pose proof (hcc3_store_step A i bB ltac:(lia)) as HS. rewrite LA in HS. change (4 * 4) with 16 in HS.
    rewrite Lc, HS. clear HS. clear Lc. subst bB.
    forward.
    set (pA := map Vubyte (words_bytes (sublist 0 (i + 1) A)) ++ Zrepeat Vundef (16 - 4 * (i + 1))).
    assert (LpA: Zlength pA = 16).
    { unfold pA. rewrite !Zlength_app, !Zlength_map, !hcc3_words_bytes_len, !Zlength_sublist, Zlength_Zrepeat by lia.
      lia. }
    pose proof (hcc3_store_step_gen pA B i [] ltac:(lia)) as HS. rewrite LpA, LB in HS.
    change (4 * 4) with 16 in HS. unfold pA in HS. rewrite <- !app_assoc in HS. fold pA in HS.
    assert (Lc: Zlength (pA ++ map Vubyte (words_bytes (sublist 0 i B)) ++ Zrepeat Vundef (16 - 4 * i) ++ []) = 32).
    { rewrite !Zlength_app, LpA, !Zlength_map, !hcc3_words_bytes_len, !Zlength_sublist, Zlength_Zrepeat,
        Zlength_nil by lia. lia. }
    unfold pA in Lc, HS. rewrite <- !app_assoc in Lc.
    forward_call (osh, out, 16 + 4 * i, map Vubyte (words_bytes (sublist 0 (i + 1) A)) ++ Zrepeat Vundef (16 - 4 * (i + 1)) ++
      map Vubyte (words_bytes (sublist 0 i B)) ++ Zrepeat Vundef (16 - 4 * i) ++ [], Znth i B).
    { entailer!. rewrite NB by lia. reflexivity. }
    { rewrite Lc. cancel. }
    rewrite Lc, HS. entailer!.
  - rewrite EH, hcc3_words_bytes_app, map_app, !sublist_same by lia. change (16 - 4 * 4) with 0.
    rewrite Zrepeat_0, !app_nil_l, !app_nil_r. clear EH EA EB NA NB. entailer!.
Qed.

Lemma haead_chacha_bodies3 : haead_hyps ->
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rc_rotl rc_rotl_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rc_qr rc_qr_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rc_rounds rc_rounds_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rc_setup rc_setup_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_ref_chacha20_block ref_chacha20_block_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_ref_hchacha20 ref_hchacha20_spec.
Proof.
  intros HH. split; [exact hcc3_rotl_body |]. split; [exact hcc3_qr_body |].
  split; [exact hcc3_rounds_body |]. split; [exact hcc3_setup_body |].
  split; [exact (hcc3_block_body HH) | exact (hcc3_hchacha_body HH)].
Qed.
