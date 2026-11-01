(* blake2s_compress_generic: one iteration of the loop over the blocks. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog3.
Require WgNoise.blake2s.code.
Require Import WgNoise.proof.blake2s.b2s_compress_stmts.
Require Import WgNoise.proof.blake2s.b2s_compress_stepstmt.
Require Import WgNoise.proof.blake2s.b2s_compress_facts.
Require Import WgNoise.proof.blake2s.b2s_compress_G3.
Require Import WgNoise.proof.blake2s.b2s_compress_round3.
Require Import WgNoise.proof.blake2s.b2s_compress_rloop3.
Require Import WgNoise.proof.blake2s.b2s_compress_feed3.
Require Import WgNoise.proof.blake2s.b2s_compress_iv3.
Require Import WgNoise.proof.blake2s.b2s_compress_tail3.

#[local] Existing Instance Blake2s.CS.

Local Open Scope Z_scope.

Lemma b2s_compress_step {Espec: OracleKind} sh ctx h t f0 dsh data n inc bs gv v_m v_v k :
  writable_share sh -> readable_share dsh -> Zlength h = 8 -> 0 <= t -> 0 <= inc <= Int.max_unsigned ->
  0 <= n -> Zlength bs = 64 * n -> 64 * n < Ptrofs.modulus -> 0 < n - k -> 0 <= k <= n ->
  semax b2s_cDelta
  (PROP ()
  LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data (offset_val (64 * k) data);
         temp code._nblocks (Vlong (Int64.repr (n - k))); temp code._inc (Vint (Int.repr inc)))
  SEP (data_at_ Tsh (tarray tuint 16) v_v; data_at_ Tsh (tarray tuint 16) v_m;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint (b2s_compress_n (Z.to_nat k) h t f0 inc bs)) ctx;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 (t + k * inc)); Vint (b2s_t1 (t + k * inc))] ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data;
       blake2s_globals gv))%assert
  b2s_step_stmt
  (normal_ret_assert
  (EX a: Z,
  PROP (0 <= a <= n)
  LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data (offset_val (64 * a) data);
         temp code._nblocks (Vlong (Int64.repr (n - a))); temp code._inc (Vint (Int.repr inc)))
  SEP (data_at_ Tsh (tarray tuint 16) v_v; data_at_ Tsh (tarray tuint 16) v_m;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint (b2s_compress_n (Z.to_nat a) h t f0 inc bs)) ctx;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 (t + a * inc)); Vint (b2s_t1 (t + a * inc))] ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data;
       blake2s_globals gv))%assert).
Proof.
intros SH SH0 H H0 H1 H2 H3 Hnmax HRE H4.
unfold b2s_step_stmt. abbreviate_semax.
forward_call (sh, ctx, t + k * inc, inc).
remember (sublist (64 * k) (64 * k + 64) bs) as blk eqn:Eblk.
remember (b2s_words blk) as mw eqn:Emw.
forward_for_simple_bound 16 (EX i: Z,
  PROP ()
  LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data (offset_val (64 * k) data);
         temp code._nblocks (Vlong (Int64.repr (n - k))); temp code._inc (Vint (Int.repr inc)))
  SEP (field_at sh t_blake2s_ctx (DOT _t)
         [Vint (b2s_t0 (t + k * inc + inc)); Vint (b2s_t1 (t + k * inc + inc))] ctx;
       data_at_ Tsh (tarray tuint 16) v_v;
       data_at Tsh (tarray tuint 16) (map Vint (sublist 0 i mw) ++ Zrepeat Vundef (16 - i)) v_m;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint (b2s_compress_n (Z.to_nat k) h t f0 inc bs)) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data;
       blake2s_globals gv))%assert.
{ entailer!. }
{ replace_SEP 5 (data_at dsh (tarray tuchar (Zlength bs)) (map Vubyte bs) data);
[ rewrite H3; entailer! | ];
forward_call (dsh, data, 64 * k + 4 * i, bs);
[ entailer! | ];
forward;
assert (Hw: Znth i mw = le32_at bs (64 * k + 4 * i))
  by (subst mw blk; rewrite b2s_words_Znth by lia; apply b2s_word_sublist; lia);
assert (Zlength mw = 16) by (rewrite Emw; apply b2s_Zlength_words);
rewrite H3; entailer!;
apply derives_refl'; f_equal; rewrite <- Hw; list_solve. }
remember (b2s_compress_n (Z.to_nat k) h t f0 inc bs) as hk eqn:Ehk.
assert (Hhk: Zlength hk = 8) by (rewrite Ehk; apply b2s_Zlength_compress_n; auto).
assert (Hmw: Zlength mw = 16) by (rewrite Emw; apply b2s_Zlength_words).
rewrite sublist_same by lia. rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
forward_for_simple_bound 8 (EX i: Z,
  PROP ()
  LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data (offset_val (64 * k) data);
         temp code._nblocks (Vlong (Int64.repr (n - k))); temp code._inc (Vint (Int.repr inc)))
  SEP (field_at sh t_blake2s_ctx (DOT _t)
         [Vint (b2s_t0 (t + k * inc + inc)); Vint (b2s_t1 (t + k * inc + inc))] ctx;
       data_at Tsh (tarray tuint 16) (map Vint (sublist 0 i hk) ++ Zrepeat Vundef (16 - i)) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data;
       blake2s_globals gv))%assert.
{ entailer!. }
{ forward; forward; entailer!; apply derives_refl'; f_equal; list_solve. }
rewrite sublist_same by lia.
match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (?a :: ?vv :: ?b :: ?c :: ?d :: ?e :: ?g :: nil)))) _ _ =>
  eapply semax_pre;
  [ | apply (b2s_iv_ok sh ctx f0 dsh data n bs gv v_m v_v (t + k * inc + inc) hk mw
               (offset_val (64 * k) data) (Vlong (Int64.repr (n - k))) (Vint (Int.repr inc))
               (map Vint hk ++ Zrepeat Vundef (16 - 8)) (Ssequence b2s_rloop_stmt b2s_feed_stmt)); auto ]
end.
{ generalize (map Vint hk ++ Zrepeat Vundef (16 - 8)); intro vv. entailer!. }
{ rewrite Zlength_app, Zlength_map, Hhk. reflexivity. }
rewrite b2s_compress_v0_eq by auto.
subst hk mw blk.
apply b2s_tail_ok; auto.
Qed.
