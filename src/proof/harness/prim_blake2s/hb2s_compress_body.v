(* bodies of the reference compression of law prim_blake2s (common.h rb2s_g, rb2s_compress) against
   model.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_spec.
Require Import WgNoise.proof.blake2s.b2s_compress_facts.
Require WgNoise.harness.x_prim_blake2s.code.

#[local] Existing Instance W_prim_blake2s.
Local Open Scope Z_scope.

Module HC.
  Definition _v := WgNoise.harness.x_prim_blake2s.code._v.
  Definition _m := WgNoise.harness.x_prim_blake2s.code._m.
  Definition _h := WgNoise.harness.x_prim_blake2s.code._h.
  Definition _block := WgNoise.harness.x_prim_blake2s.code._block.
  Definition _t := WgNoise.harness.x_prim_blake2s.code._t.
  Definition _last := WgNoise.harness.x_prim_blake2s.code._last.
  Definition _i := WgNoise.harness.x_prim_blake2s.code._i.
  Definition _r := WgNoise.harness.x_prim_blake2s.code._r.
  Definition _s := WgNoise.harness.x_prim_blake2s.code._s.
End HC.

Ltac g_st v' Hv :=
  rewrite ?Int.add_assoc;
  match goal with |- context [upd_Znth ?i (map Vint ?l) (Vint ?w)] =>
    rewrite (upd_Znth_map Vint i l w); remember (upd_Znth i l w) as v' eqn:Hv end;
  assert (Zlength v' = 16) by (subst v'; rewrite Zlength_upd_Znth; auto).

Lemma body_rb2s_g :
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_rb2s_g rb2s_g_spec.
Proof.
  start_function.
  forward. forward. forward. g_st v1 E1.
  forward. forward. forward_call (Int.xor (Znth d v1) (Znth a v1), 16). forward. g_st v2 E2.
  forward. forward. forward. g_st v3 E3.
  forward. forward. forward_call (Int.xor (Znth b v3) (Znth c v3), 12). forward. g_st v4 E4.
  forward. forward. forward. g_st v5 E5.
  forward. forward. forward_call (Int.xor (Znth d v5) (Znth a v5), 8). forward. g_st v6 E6.
  forward. forward. forward. g_st v7 E7.
  forward. forward. forward_call (Int.xor (Znth b v7) (Znth c v7), 7). forward. g_st v8 E8.
  replace v8 with (b2s_G vl a b c d x y) by (subst; reflexivity).
  clear E1 E2 E3 E4 E5 E6 E7 E8.
  entailer!.
Qed.

Ltac upd_map :=
  repeat match goal with |- context [upd_Znth ?i (map Vint ?l) (Vint ?w)] =>
    rewrite (upd_Znth_map Vint i l w) end.

Lemma hb2s_list8 {A} (l: list A) : Zlength l = 8 ->
  exists a0 a1 a2 a3 a4 a5 a6 a7, l = [a0; a1; a2; a3; a4; a5; a6; a7].
Proof.
  intros Hl. do 8 (destruct l as [|? l]; [list_solve|]). destruct l; [|list_solve].
  do 8 eexists. reflexivity.
Qed.

(* the working vector after v = h ++ IV, v12 ^= (u32)t, v13 ^= (u32)(t >> 32), v14 = ~v14 if last *)
Lemma hb2s_vinit hl t last :
  Zlength hl = 8 -> 0 <= t <= Int64.max_unsigned ->
  let v0 := hl ++ b2s_IV in
  let v1 := upd_Znth 13 (upd_Znth 12 v0 (Int.xor (Znth 12 v0) (Int.repr (Int64.unsigned (Int64.repr t)))))
    (Int.xor (Znth 13 (upd_Znth 12 v0 (Int.xor (Znth 12 v0) (Int.repr (Int64.unsigned (Int64.repr t))))))
       (Int.repr (Int64.unsigned (Int64.shru (Int64.repr t) (Int64.repr (Int.unsigned (Int.repr 32))))))) in
  (if Z.eq_dec last 0 then v1 else upd_Znth 14 v1 (Int.not (Znth 14 v1))) =
  b2s_v0 hl (b2s_t0 t) (b2s_t1 t) (if Z.eq_dec last 0 then Int.zero else Int.mone) Int.zero.
Proof.
  intros Hl Ht v0 v1.
  assert (E0: Int.repr (Int64.unsigned (Int64.repr t)) = b2s_t0 t).
  { rewrite Int64.unsigned_repr by lia. reflexivity. }
  assert (E1: Int.repr (Int64.unsigned (Int64.shru (Int64.repr t) (Int64.repr (Int.unsigned (Int.repr 32)))))
              = b2s_t1 t).
  { unfold Int64.shru. rewrite (Int64.unsigned_repr t) by lia.
    rewrite Int.unsigned_repr by rep_lia. rewrite (Int64.unsigned_repr 32) by rep_lia.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Int64.unsigned_repr.
    - reflexivity.
    - split; [apply Z.div_pos; lia|]. apply Z.le_trans with t; [apply Z.div_le_upper_bound; lia | lia]. }
  subst v1 v0. rewrite E0, E1.
  set (t0 := b2s_t0 t). set (t1 := b2s_t1 t). clearbody t0 t1.
  unfold b2s_v0.
  set (i0 := Znth 0 b2s_IV). set (i1 := Znth 1 b2s_IV). set (i2 := Znth 2 b2s_IV). set (i3 := Znth 3 b2s_IV).
  set (i4 := Znth 4 b2s_IV). set (i5 := Znth 5 b2s_IV). set (i6 := Znth 6 b2s_IV). set (i7 := Znth 7 b2s_IV).
  assert (HIV: b2s_IV = [i0; i1; i2; i3; i4; i5; i6; i7]) by reflexivity.
  clearbody i0 i1 i2 i3 i4 i5 i6 i7. rewrite HIV. clear HIV.
  destruct (hb2s_list8 hl Hl) as (h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & ->).
  destruct (Z.eq_dec last 0); rewrite ?Int.xor_zero; reflexivity.
Qed.

Lemma hb2s_sigma_row i : 0 <= i < 10 ->
  Zlength (Znth i b2s_sigma) = 16 /\ Forall (fun z => 0 <= z < 16) (Znth i b2s_sigma).
Proof.
  intros Hi.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) as Hc by lia.
  repeat destruct Hc as [Hc | Hc]; subst i; simpl; split; try reflexivity;
    repeat (apply Forall_cons; [lia|]); apply Forall_nil.
Qed.

(* for ANY inhabitants (VST's loads use the reptype defaults) *)
Lemma hb2s_sigma_val_Znth (d: val) (dl: list val) i k : 0 <= i < 10 -> 0 <= k < 16 ->
  @Znth val d k (@Znth (list val) dl i blake2s_sigma_val) = Vint (Int.repr (Znth k (Znth i b2s_sigma))).
Proof.
  intros Hi Hk.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) as Hc by lia.
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/
          k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15) as Hc' by lia.
  repeat destruct Hc as [Hc | Hc]; subst i; repeat destruct Hc' as [Hc' | Hc']; subst k; reflexivity.
Qed.

Lemma hb2s_sigma_range i k : 0 <= i < 10 -> 0 <= k < 16 -> 0 <= Znth k (Znth i b2s_sigma) < 16.
Proof.
  intros Hi Hk. destruct (hb2s_sigma_row i Hi) as [Hl Hf].
  rewrite Forall_Znth in Hf. apply Hf. lia.
Qed.

Ltac sig_ld i k :=
  forward;
  [ rewrite (hb2s_sigma_val_Znth _ _ i k) by lia;
    let Hk := fresh in pose proof (hb2s_sigma_range i k ltac:(lia) ltac:(lia)) as Hk; entailer!; rep_lia
  | rewrite (hb2s_sigma_val_Znth _ _ i k) by lia ].

(* one rb2s_g call of a round: loads s[k], m[s[k]], s[k1], m[s[k1]], the call; the new state w' *)
Ltac g_grp i mw k k1 a b c d w w' Ew :=
  pose proof (hb2s_sigma_range i k ltac:(lia) ltac:(lia));
  pose proof (hb2s_sigma_range i k1 ltac:(lia) ltac:(lia));
  sig_ld i k; forward; sig_ld i k1; forward;
  match goal with |- context [data_at Tsh (tarray tuint 16) (map Vint w) ?vv] =>
    forward_call (Tsh, vv, w, a, b, c, d, Znth (Znth k (Znth i b2s_sigma)) mw,
                  Znth (Znth k1 (Znth i b2s_sigma)) mw) end;
  let Hl := fresh "Hl" in
  assert (Hl: Zlength (b2s_G w a b c d (Znth (Znth k (Znth i b2s_sigma)) mw)
                         (Znth (Znth k1 (Znth i b2s_sigma)) mw)) = 16)
    by (rewrite b2s_Zlength_G; auto);
  remember (b2s_G w a b c d (Znth (Znth k (Znth i b2s_sigma)) mw) (Znth (Znth k1 (Znth i b2s_sigma)) mw))
    as w' eqn:Ew;
  apply (fun H => conj H I) in Ew.

(* simpl on Int64.unsigned (Int64.shru T 32) (the cast of t >> 32) diverges: keep shru folded *)
Local Opaque Int64.shru.

(* the statements of rb2s_compress: the loop over the rounds, and one round (its body) *)
Definition hb2s_cbody : statement :=
  Eval cbv beta iota delta [WgNoise.harness.x_prim_blake2s.code.f_rb2s_compress fn_body]
  in fn_body WgNoise.harness.x_prim_blake2s.code.f_rb2s_compress.

Definition hb2s_rloop_stmt : statement :=
  Eval cbv beta iota delta [hb2s_cbody] in
  match hb2s_cbody with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence r _))))) => r
  | _ => Sskip end.

Definition hb2s_round_stmt : statement :=
  Eval cbv beta iota delta [hb2s_rloop_stmt] in
  match hb2s_rloop_stmt with
  | Ssequence _ (Sloop (Ssequence _ b) _) => b
  | _ => Sskip end.

Definition hb2s_cDelta : tycontext :=
  func_tycontext WgNoise.harness.x_prim_blake2s.code.f_rb2s_compress hb2s_V hb2s_Gprog nil.

Definition hb2s_gstate (i: Z) (w mw: list int) (vv vm hp: val) (gv: globals) (FR: mpred) : environ -> mpred :=
  PROP ()
  LOCAL (temp HC._s (field_address (tarray (tarray tuchar 16) 10) [ArraySubsc i] (gv HB._RB2S_SIGMA));
         temp HC._r (Vint (Int.repr i)); lvar HC._v (tarray tuint 16) vv; lvar HC._m (tarray tuint 16) vm;
         gvars gv; temp HC._h hp)
  SEP (data_at Tsh (tarray tuint 16) (map Vint w) vv; data_at Tsh (tarray tuint 16) (map Vint mw) vm;
       data_at Ers (tarray (tarray tuchar 16) 10) blake2s_sigma_val (gv HB._RB2S_SIGMA); FR).

Definition hb2s_G1_stmt : statement :=
  Eval cbv beta iota delta [hb2s_round_stmt] in
  match hb2s_round_stmt with Ssequence _ (Ssequence g _) => g | _ => Sskip end.

Definition hb2s_G2_stmt : statement :=
  Eval cbv beta iota delta [hb2s_round_stmt] in
  match hb2s_round_stmt with Ssequence _ (Ssequence _ (Ssequence g _)) => g | _ => Sskip end.

Definition hb2s_G3_stmt : statement :=
  Eval cbv beta iota delta [hb2s_round_stmt] in
  match hb2s_round_stmt with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence g _))) => g | _ => Sskip end.

Definition hb2s_G4_stmt : statement :=
  Eval cbv beta iota delta [hb2s_round_stmt] in
  match hb2s_round_stmt with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence g _)))) => g | _ => Sskip end.

Definition hb2s_G5_stmt : statement :=
  Eval cbv beta iota delta [hb2s_round_stmt] in
  match hb2s_round_stmt with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence g _))))) => g | _ => Sskip end.

Definition hb2s_G6_stmt : statement :=
  Eval cbv beta iota delta [hb2s_round_stmt] in
  match hb2s_round_stmt with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence g _)))))) => g | _ => Sskip end.

Definition hb2s_G7_stmt : statement :=
  Eval cbv beta iota delta [hb2s_round_stmt] in
  match hb2s_round_stmt with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence g _))))))) => g | _ => Sskip end.

Definition hb2s_G8_stmt : statement :=
  Eval cbv beta iota delta [hb2s_round_stmt] in
  match hb2s_round_stmt with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ g))))))) => g | _ => Sskip end.

Lemma hb2s_G1_ok {Espec: OracleKind} i mw w vv vm hp gv FR :
  0 <= i < 10 -> Zlength mw = 16 -> Zlength w = 16 ->
  semax hb2s_cDelta (hb2s_gstate i w mw vv vm hp gv FR) hb2s_G1_stmt
    (normal_ret_assert (hb2s_gstate i (b2s_G w 0 4 8 12 (Znth (Znth 0 (Znth i b2s_sigma)) mw)
       (Znth (Znth 1 (Znth i b2s_sigma)) mw)) mw vv vm hp gv FR)).
Proof.
  intros Hi Hmw Hw. unfold hb2s_gstate, hb2s_G1_stmt. abbreviate_semax.
  g_grp i mw 0 1 0 4 8 12 w w' Ew.
  clear Ew. entailer!.
Qed.

Lemma hb2s_G2_ok {Espec: OracleKind} i mw w vv vm hp gv FR :
  0 <= i < 10 -> Zlength mw = 16 -> Zlength w = 16 ->
  semax hb2s_cDelta (hb2s_gstate i w mw vv vm hp gv FR) hb2s_G2_stmt
    (normal_ret_assert (hb2s_gstate i (b2s_G w 1 5 9 13 (Znth (Znth 2 (Znth i b2s_sigma)) mw)
       (Znth (Znth 3 (Znth i b2s_sigma)) mw)) mw vv vm hp gv FR)).
Proof.
  intros Hi Hmw Hw. unfold hb2s_gstate, hb2s_G2_stmt. abbreviate_semax.
  g_grp i mw 2 3 1 5 9 13 w w' Ew.
  clear Ew. entailer!.
Qed.

Lemma hb2s_G3_ok {Espec: OracleKind} i mw w vv vm hp gv FR :
  0 <= i < 10 -> Zlength mw = 16 -> Zlength w = 16 ->
  semax hb2s_cDelta (hb2s_gstate i w mw vv vm hp gv FR) hb2s_G3_stmt
    (normal_ret_assert (hb2s_gstate i (b2s_G w 2 6 10 14 (Znth (Znth 4 (Znth i b2s_sigma)) mw)
       (Znth (Znth 5 (Znth i b2s_sigma)) mw)) mw vv vm hp gv FR)).
Proof.
  intros Hi Hmw Hw. unfold hb2s_gstate, hb2s_G3_stmt. abbreviate_semax.
  g_grp i mw 4 5 2 6 10 14 w w' Ew.
  clear Ew. entailer!.
Qed.

Lemma hb2s_G4_ok {Espec: OracleKind} i mw w vv vm hp gv FR :
  0 <= i < 10 -> Zlength mw = 16 -> Zlength w = 16 ->
  semax hb2s_cDelta (hb2s_gstate i w mw vv vm hp gv FR) hb2s_G4_stmt
    (normal_ret_assert (hb2s_gstate i (b2s_G w 3 7 11 15 (Znth (Znth 6 (Znth i b2s_sigma)) mw)
       (Znth (Znth 7 (Znth i b2s_sigma)) mw)) mw vv vm hp gv FR)).
Proof.
  intros Hi Hmw Hw. unfold hb2s_gstate, hb2s_G4_stmt. abbreviate_semax.
  g_grp i mw 6 7 3 7 11 15 w w' Ew.
  clear Ew. entailer!.
Qed.

Lemma hb2s_G5_ok {Espec: OracleKind} i mw w vv vm hp gv FR :
  0 <= i < 10 -> Zlength mw = 16 -> Zlength w = 16 ->
  semax hb2s_cDelta (hb2s_gstate i w mw vv vm hp gv FR) hb2s_G5_stmt
    (normal_ret_assert (hb2s_gstate i (b2s_G w 0 5 10 15 (Znth (Znth 8 (Znth i b2s_sigma)) mw)
       (Znth (Znth 9 (Znth i b2s_sigma)) mw)) mw vv vm hp gv FR)).
Proof.
  intros Hi Hmw Hw. unfold hb2s_gstate, hb2s_G5_stmt. abbreviate_semax.
  g_grp i mw 8 9 0 5 10 15 w w' Ew.
  clear Ew. entailer!.
Qed.

Lemma hb2s_G6_ok {Espec: OracleKind} i mw w vv vm hp gv FR :
  0 <= i < 10 -> Zlength mw = 16 -> Zlength w = 16 ->
  semax hb2s_cDelta (hb2s_gstate i w mw vv vm hp gv FR) hb2s_G6_stmt
    (normal_ret_assert (hb2s_gstate i (b2s_G w 1 6 11 12 (Znth (Znth 10 (Znth i b2s_sigma)) mw)
       (Znth (Znth 11 (Znth i b2s_sigma)) mw)) mw vv vm hp gv FR)).
Proof.
  intros Hi Hmw Hw. unfold hb2s_gstate, hb2s_G6_stmt. abbreviate_semax.
  g_grp i mw 10 11 1 6 11 12 w w' Ew.
  clear Ew. entailer!.
Qed.

Lemma hb2s_G7_ok {Espec: OracleKind} i mw w vv vm hp gv FR :
  0 <= i < 10 -> Zlength mw = 16 -> Zlength w = 16 ->
  semax hb2s_cDelta (hb2s_gstate i w mw vv vm hp gv FR) hb2s_G7_stmt
    (normal_ret_assert (hb2s_gstate i (b2s_G w 2 7 8 13 (Znth (Znth 12 (Znth i b2s_sigma)) mw)
       (Znth (Znth 13 (Znth i b2s_sigma)) mw)) mw vv vm hp gv FR)).
Proof.
  intros Hi Hmw Hw. unfold hb2s_gstate, hb2s_G7_stmt. abbreviate_semax.
  g_grp i mw 12 13 2 7 8 13 w w' Ew.
  clear Ew. entailer!.
Qed.

Lemma hb2s_G8_ok {Espec: OracleKind} i mw w vv vm hp gv FR :
  0 <= i < 10 -> Zlength mw = 16 -> Zlength w = 16 ->
  semax hb2s_cDelta (hb2s_gstate i w mw vv vm hp gv FR) hb2s_G8_stmt
    (normal_ret_assert (hb2s_gstate i (b2s_G w 3 4 9 14 (Znth (Znth 14 (Znth i b2s_sigma)) mw)
       (Znth (Znth 15 (Znth i b2s_sigma)) mw)) mw vv vm hp gv FR)).
Proof.
  intros Hi Hmw Hw. unfold hb2s_gstate, hb2s_G8_stmt. abbreviate_semax.
  g_grp i mw 14 15 3 4 9 14 w w' Ew.
  clear Ew. entailer!.
Qed.

Definition hb2s_rstate (r: Z) (v mw: list int) (vv vm hp: val) (gv: globals) (FR: mpred) : environ -> mpred :=
  PROP ()
  LOCAL (temp HC._r (Vint (Int.repr r)); lvar HC._v (tarray tuint 16) vv; lvar HC._m (tarray tuint 16) vm;
         gvars gv; temp HC._h hp)
  SEP (data_at Tsh (tarray tuint 16) (map Vint v) vv; data_at Tsh (tarray tuint 16) (map Vint mw) vm;
       data_at Ers (tarray (tarray tuchar 16) 10) blake2s_sigma_val (gv HB._RB2S_SIGMA); FR).

Definition hb2s_sset_stmt : statement :=
  Eval cbv beta iota delta [hb2s_round_stmt] in
  match hb2s_round_stmt with Ssequence g _ => g | _ => Sskip end.

Lemma hb2s_round_stmt_eq : hb2s_round_stmt =
  Ssequence hb2s_sset_stmt (Ssequence hb2s_G1_stmt (Ssequence hb2s_G2_stmt (Ssequence hb2s_G3_stmt
  (Ssequence hb2s_G4_stmt (Ssequence hb2s_G5_stmt (Ssequence hb2s_G6_stmt
  (Ssequence hb2s_G7_stmt hb2s_G8_stmt))))))).
Proof. reflexivity. Qed.

Lemma hb2s_sset_ok {Espec: OracleKind} i v mw vv vm hp gv FR :
  0 <= i < 10 ->
  semax hb2s_cDelta (hb2s_rstate i v mw vv vm hp gv FR) hb2s_sset_stmt
    (normal_ret_assert (hb2s_gstate i v mw vv vm hp gv FR)).
Proof.
  intros H3. unfold hb2s_rstate, hb2s_gstate, hb2s_sset_stmt. abbreviate_semax.
  assert_PROP (field_compatible (tarray (tarray tuchar 16) 10) [] (gv HB._RB2S_SIGMA)) as FC by entailer!.
  assert (Es: force_val (sem_binary_operation' Oadd (tarray (tarray tuchar 16) 10) tint (gv HB._RB2S_SIGMA)
                (Vint (Int.repr i))) = field_address (tarray (tarray tuchar 16) 10) [ArraySubsc i] (gv HB._RB2S_SIGMA)).
  { rewrite field_address_offset by auto with field_compatible. destruct FC as [Hp _].
    destruct (gv HB._RB2S_SIGMA); try contradiction. simpl.
    unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia. rewrite ptrofs_mul_repr. do 3 f_equal; try lia. }
  forward. change (gv code._RB2S_SIGMA) with (gv HB._RB2S_SIGMA). rewrite Es. clear Es.
  entailer!.
Qed.

Lemma hb2s_round_ok {Espec: OracleKind} i mw v vv vm hp gv FR :
  0 <= i < 10 -> Zlength mw = 16 -> Zlength v = 16 ->
  semax hb2s_cDelta (hb2s_rstate i v mw vv vm hp gv FR) hb2s_round_stmt
    (normal_ret_assert (hb2s_gstate i (b2s_round mw v (Znth i b2s_sigma)) mw vv vm hp gv FR)).
Proof.
  intros Hi Hmw Hv. rewrite hb2s_round_stmt_eq.
  eapply semax_seq'. { apply hb2s_sset_ok; auto. }
  eapply semax_seq'. { apply hb2s_G1_ok; auto. }
  eapply semax_seq'. { apply hb2s_G2_ok; auto. rewrite !b2s_Zlength_G; auto. }
  eapply semax_seq'. { apply hb2s_G3_ok; auto. rewrite !b2s_Zlength_G; auto. }
  eapply semax_seq'. { apply hb2s_G4_ok; auto. rewrite !b2s_Zlength_G; auto. }
  eapply semax_seq'. { apply hb2s_G5_ok; auto. rewrite !b2s_Zlength_G; auto. }
  eapply semax_seq'. { apply hb2s_G6_ok; auto. rewrite !b2s_Zlength_G; auto. }
  eapply semax_seq'. { apply hb2s_G7_ok; auto. rewrite !b2s_Zlength_G; auto. }
  unfold b2s_round. cbv zeta beta.
  apply hb2s_G8_ok; auto. rewrite !b2s_Zlength_G; auto.
Qed.

Lemma hb2s_rloop_ok {Espec: OracleKind} mw vi vv vm hp gv FR :
  Zlength mw = 16 -> Zlength vi = 16 ->
  semax hb2s_cDelta
    (PROP ()
     LOCAL (lvar HC._v (tarray tuint 16) vv; lvar HC._m (tarray tuint 16) vm; gvars gv; temp HC._h hp)
     SEP (data_at Tsh (tarray tuint 16) (map Vint vi) vv; data_at Tsh (tarray tuint 16) (map Vint mw) vm;
          data_at Ers (tarray (tarray tuchar 16) 10) blake2s_sigma_val (gv HB._RB2S_SIGMA); FR))
    hb2s_rloop_stmt
    (normal_ret_assert
    (PROP ()
     LOCAL (temp HC._r (Vint (Int.repr 10));
            lvar HC._v (tarray tuint 16) vv; lvar HC._m (tarray tuint 16) vm; gvars gv; temp HC._h hp)
     SEP (data_at Tsh (tarray tuint 16) (map Vint (b2s_rounds mw vi 10)) vv;
          data_at Tsh (tarray tuint 16) (map Vint mw) vm;
          data_at Ers (tarray (tarray tuchar 16) 10) blake2s_sigma_val (gv HB._RB2S_SIGMA); FR))).
Proof.
  intros Hmw Hvi.
  unfold hb2s_rloop_stmt. abbreviate_semax.
  assert (E0: b2s_rounds mw vi 0 = vi) by reflexivity.
  rewrite <- E0.
  forward_for_simple_bound 10 (EX r: Z,
    PROP ()
    LOCAL (lvar HC._v (tarray tuint 16) vv; lvar HC._m (tarray tuint 16) vm; gvars gv; temp HC._h hp)
    SEP (data_at Tsh (tarray tuint 16) (map Vint (b2s_rounds mw vi r)) vv;
         data_at Tsh (tarray tuint 16) (map Vint mw) vm;
         data_at Ers (tarray (tarray tuchar 16) 10) blake2s_sigma_val (gv HB._RB2S_SIGMA); FR))%assert.
  { entailer!. }
  { cbv beta.
    eapply semax_pre; [ | eapply semax_post; [ | | | |
        apply (hb2s_round_ok i mw (b2s_rounds mw vi i) vv vm hp gv FR) ] ].
    { unfold hb2s_rstate. entailer!. }
    { unfold POSTCONDITION, abbreviate. simpl_ret_assert. rewrite <- b2s_rounds_succ by lia.
      unfold hb2s_gstate. entailer!. }
    { unfold POSTCONDITION, abbreviate. simpl_ret_assert. normalize. }
    { unfold POSTCONDITION, abbreviate. simpl_ret_assert. normalize. }
    { intros. unfold POSTCONDITION, abbreviate. simpl_ret_assert. normalize. }
    { lia. }
    { auto. }
    { rewrite b2s_Zlength_rounds; auto. } }
  entailer!.
Qed.

Lemma body_rb2s_compress :
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_rb2s_compress rb2s_compress_spec.
Proof.
  start_function.
  unfold hb2s_globals. Intros.
  forward_for_simple_bound 16 (EX i: Z,
    PROP ()
    LOCAL (lvar HC._v (tarray tuint 16) v_v; lvar HC._m (tarray tuint 16) v_m; gvars gv;
           temp HC._h hp; temp HC._block bp; temp HC._t (Vlong (Int64.repr t));
           temp HC._last (Vint (Int.repr last)))
    SEP (data_at_ Tsh (tarray tuint 16) v_v;
         data_at Tsh (tarray tuint 16) (map Vint (sublist 0 i (b2s_words blk)) ++ Zrepeat Vundef (16 - i)) v_m;
         data_at shh (tarray tuint 8) (map Vint hl) hp;
         data_at shb (tarray tuchar 64) (map Vubyte blk) bp;
         data_at Ers (tarray tuint 8) (map Vint b2s_IV) (gv HB._RB2S_IV);
         data_at Ers (tarray (tarray tuchar 16) 10) blake2s_sigma_val (gv HB._RB2S_SIGMA)))%assert.
  { entailer!. }
  { rewrite <- H0. forward_call (shb, bp, 4 * i, blk). { entailer!. }
    forward.
    entailer!.
    rewrite H0. apply derives_refl'. rewrite sepcon_comm. f_equal. f_equal.
    pose proof (b2s_Zlength_words blk).
    rewrite (sublist_split 0 i (i+1)) by lia. rewrite (sublist_len_1 i) by lia.
    rewrite b2s_words_Znth by lia. unfold b2s_word. list_solve. }
  rewrite sublist_same by (rewrite ?b2s_Zlength_words; lia). rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
  assert (Hmw: Zlength (b2s_words blk) = 16) by apply b2s_Zlength_words.
  remember (b2s_words blk) as mw eqn:Emw. assert (Hmw': mw = b2s_words blk /\ True) by auto. clear Emw.
  forward_for_simple_bound 8 (EX i: Z,
    PROP ()
    LOCAL (lvar HC._v (tarray tuint 16) v_v; lvar HC._m (tarray tuint 16) v_m; gvars gv;
           temp HC._h hp; temp HC._block bp; temp HC._t (Vlong (Int64.repr t));
           temp HC._last (Vint (Int.repr last)))
    SEP (data_at Tsh (tarray tuint 16) (map Vint (sublist 0 i hl) ++ Zrepeat Vundef (8 - i) ++
                                        map Vint (sublist 0 i b2s_IV) ++ Zrepeat Vundef (8 - i)) v_v;
         data_at Tsh (tarray tuint 16) (map Vint mw) v_m;
         data_at shh (tarray tuint 8) (map Vint hl) hp;
         data_at shb (tarray tuchar 64) (map Vubyte blk) bp;
         data_at Ers (tarray tuint 8) (map Vint b2s_IV) (gv HB._RB2S_IV);
         data_at Ers (tarray (tarray tuchar 16) 10) blake2s_sigma_val (gv HB._RB2S_SIGMA)))%assert.
  { entailer!. }
  { forward. forward. forward. forward.
    entailer!.
    apply derives_refl'. f_equal. assert (Zlength b2s_IV = 8) by reflexivity.
    generalize dependent b2s_IV; intros iv; intros.
    rewrite (sublist_split 0 i (i+1) hl) by lia. rewrite (sublist_split 0 i (i+1) iv) by lia.
    rewrite (sublist_len_1 i hl) by lia. rewrite (sublist_len_1 i iv) by lia. list_solve. }
  rewrite !sublist_same by (rewrite ?H; reflexivity). rewrite Z.sub_diag, Zrepeat_0, !app_nil_r, app_nil_l.
  rewrite <- map_app.
  assert (Hv0: Zlength (hl ++ b2s_IV) = 16) by (rewrite Zlength_app, H; reflexivity).
  remember (hl ++ b2s_IV) as v0 eqn:Ev0. assert (Ev0': v0 = hl ++ b2s_IV /\ True) by auto. clear Ev0.
  remember (Int64.repr t) as T eqn:ET. assert (ET': T = Int64.repr t /\ True) by auto. clear ET.
  forward. forward. upd_map. forward. forward. upd_map.
  match goal with |- context [data_at Tsh (tarray tuint 16) (map Vint ?l) v_v] =>
    remember l as v1 eqn:Ev1 end.
  assert (Hv1: Zlength v1 = 16) by (rewrite Ev1; rewrite !Zlength_upd_Znth; auto).
  assert (Ev1': v1 = upd_Znth 13 (upd_Znth 12 v0 (Int.xor (Znth 12 v0) (Int.repr (Int64.unsigned T))))
    (Int.xor (Znth 13 (upd_Znth 12 v0 (Int.xor (Znth 12 v0) (Int.repr (Int64.unsigned T)))))
       (Int.repr (Int64.unsigned (Int64.shru T (Int64.repr (Int.unsigned (Int.repr 32))))))) /\ True)
    by (split; [exact Ev1 | auto]).
  clear Ev1.
  forward_if (PROP ()
    LOCAL (lvar HC._v (tarray tuint 16) v_v; lvar HC._m (tarray tuint 16) v_m; gvars gv; temp HC._h hp)
    SEP (data_at Tsh (tarray tuint 16)
           (map Vint (if Z.eq_dec last 0 then v1 else upd_Znth 14 v1 (Int.not (Znth 14 v1)))) v_v;
         data_at Tsh (tarray tuint 16) (map Vint mw) v_m;
         data_at shh (tarray tuint 8) (map Vint hl) hp;
         data_at shb (tarray tuchar 64) (map Vubyte blk) bp;
         data_at Ers (tarray tuint 8) (map Vint b2s_IV) (gv HB._RB2S_IV);
         data_at Ers (tarray (tarray tuchar 16) 10) blake2s_sigma_val (gv HB._RB2S_SIGMA))).
  { forward. forward. upd_map. entailer!.
    destruct (Z.eq_dec last 0); [subst; contradiction | apply derives_refl]. }
  { forward. entailer!.
    destruct (Z.eq_dec last 0); [apply derives_refl | ].
    exfalso. apply n. apply repr_inj_signed; [rep_lia | rep_lia | auto]. }
  destruct Ev1' as [Ev1 _]. destruct Ev0' as [Ev0 _]. destruct ET' as [ET _]. subst v1 v0 T.
  pose proof (hb2s_vinit hl t last H H1) as Hvi. cbv zeta in Hvi. rewrite Hvi. clear Hvi Hv1 Hv0.
  assert (Hvi: Zlength (b2s_v0 hl (b2s_t0 t) (b2s_t1 t) (if Z.eq_dec last 0 then Int.zero else Int.mone)
                          Int.zero) = 16) by (unfold b2s_v0; rewrite Zlength_app, H; reflexivity).
  remember (b2s_v0 hl (b2s_t0 t) (b2s_t1 t) (if Z.eq_dec last 0 then Int.zero else Int.mone) Int.zero)
    as vi eqn:Evi.
  assert (Evi': vi = b2s_v0 hl (b2s_t0 t) (b2s_t1 t) (if Z.eq_dec last 0 then Int.zero else Int.mone)
                       Int.zero /\ True) by auto.
  clear Evi.
  eapply semax_seq'.
  { eapply semax_pre; [ | apply (hb2s_rloop_ok mw vi v_v v_m hp gv
      (data_at shh (tarray tuint 8) (map Vint hl) hp * data_at shb (tarray tuchar 64) (map Vubyte blk) bp *
       data_at Ers (tarray tuint 8) (map Vint b2s_IV) (gv HB._RB2S_IV))%logic); auto ].
    entailer!. }
  flatten_sepcon_in_SEP. flatten_sepcon_in_SEP. unfold MORE_COMMANDS, abbreviate.
  assert (Hvf: Zlength (b2s_rounds mw vi 10) = 16) by (rewrite b2s_Zlength_rounds; auto).
  remember (b2s_rounds mw vi 10) as vf eqn:Evf. apply (fun H => conj H I) in Evf.
  forward_for_simple_bound 8 (EX i: Z,
    PROP ()
    LOCAL (lvar HC._v (tarray tuint 16) v_v; lvar HC._m (tarray tuint 16) v_m; gvars gv; temp HC._h hp)
    SEP (data_at Tsh (tarray tuint 16) (map Vint vf) v_v;
         data_at Tsh (tarray tuint 16) (map Vint mw) v_m;
         data_at shh (tarray tuint 8) (map Vint (sublist 0 i (b2s_feed hl vf) ++ sublist i 8 hl)) hp;
         data_at shb (tarray tuchar 64) (map Vubyte blk) bp;
         data_at Ers (tarray tuint 8) (map Vint b2s_IV) (gv HB._RB2S_IV);
         data_at Ers (tarray (tarray tuchar 16) 10) blake2s_sigma_val (gv HB._RB2S_SIGMA)))%assert.
  { entailer!. rewrite sublist_nil, app_nil_l, sublist_same by lia. auto. }
  { assert (Hf: Zlength (b2s_feed hl vf) = 8) by apply b2s_Zlength_feed.
    forward.
    autorewrite with sublist.
    forward. forward. forward.
    entailer!.
    apply derives_refl'. f_equal.
    rewrite upd_Znth_map. f_equal.
    rewrite (sublist_split 0 i (i + 1) (b2s_feed hl vf)) by lia.
    rewrite (sublist_len_1 i (b2s_feed hl vf)) by lia.
    rewrite b2s_Znth_feed by lia.
    list_solve. }
  assert (Ef: b2s_compress_block hl blk t (if Z.eq_dec last 0 then Int.zero else Int.mone) = b2s_feed hl vf).
  { destruct Evf as [Evf _], Evi' as [Evi _], Hmw' as [Emw _]. subst vf vi mw.
    unfold b2s_compress_block, b2s_compress. reflexivity. }
  rewrite Ef. rewrite sublist_same by (rewrite ?b2s_Zlength_feed; lia).
  rewrite sublist_nil, app_nil_r.
  unfold hb2s_globals. entailer!.
Qed.

Lemma hb2s_compress_bodies :
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_rb2s_g rb2s_g_spec /\
  semax_body hb2s_V hb2s_Gprog WgNoise.harness.x_prim_blake2s.code.f_rb2s_compress rb2s_compress_spec.
Proof.
  split; [exact body_rb2s_g | exact body_rb2s_compress].
Qed.
