(* blake2s_compress_generic: after the rounds, the feed-forward h[i] ^= v[i] ^ v[i + 8], data += 64,
   --nblocks, up to the loop invariant of the next block; in the context b2s_Gprog5. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog5.
Require WgNoise.blake2s.code.
Require Import WgNoise.proof.blake2s.b2s_compress_stepstmt.
Require Import WgNoise.proof.blake2s.b2s_compress_facts.
Require Import WgNoise.proof.blake2s.b2s_compress_G3.
Require Import WgNoise.proof.blake2s.b2s_compress_G5.

#[local] Existing Instance Blake2s.CS.
Local Open Scope Z_scope.

Lemma b2s_feed5_ok {Espec: OracleKind} sh ctx h t f0 dsh data n inc bs gv v_m v_v k hk vf mw :
  writable_share sh -> 0 <= n -> Zlength bs = 64 * n -> 0 < n - k -> 0 <= k <= n ->
  Zlength hk = 8 -> Zlength vf = 16 ->
  b2s_feed hk vf = b2s_compress_n (Z.to_nat (k + 1)) h t f0 inc bs ->
  semax b2s_cDelta5
  (PROP ()
   LOCAL (temp code._r (Vint (Int.repr 10));
          lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
          temp code._ctx ctx; temp code._data (offset_val (64 * k) data);
          temp code._nblocks (Vlong (Int64.repr (n - k))); temp code._inc (Vint (Int.repr inc)))
   SEP (data_at Tsh (tarray tuint 16) (map Vint vf) v_v;
        data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
        field_at sh t_blake2s_ctx (DOT _t)
          [Vint (b2s_t0 (t + k * inc + inc)); Vint (b2s_t1 (t + k * inc + inc))] ctx;
        field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
        field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
        data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert
  b2s_feed_stmt
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
intros SH H2 H3 HRE H4 Hhk Hvf Hh.
unfold b2s_feed_stmt. abbreviate_semax.
assert (Hhn: Zlength (b2s_feed hk vf) = 8) by apply b2s_Zlength_feed.
forward_for_simple_bound 8 (EX i: Z,
  PROP ()
  LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data (offset_val (64 * k) data);
         temp code._nblocks (Vlong (Int64.repr (n - k))); temp code._inc (Vint (Int.repr inc)))
  SEP (data_at Tsh (tarray tuint 16) (map Vint vf) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m;
       blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t)
         [Vint (b2s_t0 (t + k * inc + inc)); Vint (b2s_t1 (t + k * inc + inc))] ctx;
       field_at sh t_blake2s_ctx (DOT _h)
         (map Vint (sublist 0 i (b2s_feed hk vf) ++ sublist i 8 hk)) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert.
{ entailer!. apply derives_refl'. f_equal. list_solve. }
{ assert (Zlength (sublist 0 i (b2s_feed hk vf) ++ sublist i 8 hk) = 8) by list_solve.
  assert (Hz: Znth i (sublist 0 i (b2s_feed hk vf) ++ sublist i 8 hk) = Znth i hk) by list_solve.
  assert (Hn: Znth i (b2s_feed hk vf) = Int.xor (Znth i hk) (Int.xor (Znth i vf) (Znth (i + 8) vf)))
    by (apply b2s_Znth_feed; lia).
  forward. rewrite Hz.
  forward. forward. forward.
  entailer!.
  apply derives_refl'. f_equal.
  rewrite <- Hn. list_solve. }
rewrite sublist_same by lia. rewrite sublist_nil, app_nil_r, Hh.
replace (t + k * inc + inc) with (t + (k + 1) * inc) by ring.
forward. forward. Exists (k + 1). entailer!.
split.
- rewrite Z.mul_add_distr_l, Z.mul_1_r. reflexivity.
- f_equal. f_equal. lia.
Qed.
