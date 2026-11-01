(* blake2s_compress_generic: v[8..15] = IV (v[12..15] xor t0, t1, f0, f1), then any rest; in the
   context b2s_Gprog5 (the statements b2s_iv_st8 .. b2s_iv_st15 are those of b2s_compress_iv3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog5.
Require WgNoise.blake2s.code.
Require Import WgNoise.proof.blake2s.b2s_compress_stepstmt.
Require Import WgNoise.proof.blake2s.b2s_compress_prestmt.
Require Import WgNoise.proof.blake2s.b2s_compress_facts.
Require Import WgNoise.proof.blake2s.b2s_compress_G3.
Require Import WgNoise.proof.blake2s.b2s_compress_iv3.
Require Import WgNoise.proof.blake2s.b2s_compress_G5.

#[local] Existing Instance Blake2s.CS.
Local Open Scope Z_scope.

Lemma b2s_iv5_st8_ok {Espec: OracleKind} sh ctx f0 dsh data n bs gv v_m v_v tt hk mw dp nb ic (vl: list val) rest R :
  writable_share sh -> Zlength vl = 16 ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (upd_Znth 8 vl (Vint (Int.repr 1779033703))) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert rest R ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (vl) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert (Ssequence b2s_iv_st8 rest) R.
Proof.
intros SH Hl Hrest.
unfold b2s_iv_st8. simpl. abbreviate_semax.
repeat forward.
eapply semax_pre; [ | exact Hrest ].
generalize (upd_Znth 8 vl (Vint (Int.repr 1779033703))); intro vv.
entailer!.
Qed.

Lemma b2s_iv5_st9_ok {Espec: OracleKind} sh ctx f0 dsh data n bs gv v_m v_v tt hk mw dp nb ic (vl: list val) rest R :
  writable_share sh -> Zlength vl = 16 ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (upd_Znth 9 vl (Vint (Int.repr (-1150833019)))) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert rest R ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (vl) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert (Ssequence b2s_iv_st9 rest) R.
Proof.
intros SH Hl Hrest.
unfold b2s_iv_st9. simpl. abbreviate_semax.
repeat forward.
eapply semax_pre; [ | exact Hrest ].
generalize (upd_Znth 9 vl (Vint (Int.repr (-1150833019)))); intro vv.
entailer!.
Qed.

Lemma b2s_iv5_st10_ok {Espec: OracleKind} sh ctx f0 dsh data n bs gv v_m v_v tt hk mw dp nb ic (vl: list val) rest R :
  writable_share sh -> Zlength vl = 16 ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (upd_Znth 10 vl (Vint (Int.repr 1013904242))) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert rest R ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (vl) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert (Ssequence b2s_iv_st10 rest) R.
Proof.
intros SH Hl Hrest.
unfold b2s_iv_st10. simpl. abbreviate_semax.
repeat forward.
eapply semax_pre; [ | exact Hrest ].
generalize (upd_Znth 10 vl (Vint (Int.repr 1013904242))); intro vv.
entailer!.
Qed.

Lemma b2s_iv5_st11_ok {Espec: OracleKind} sh ctx f0 dsh data n bs gv v_m v_v tt hk mw dp nb ic (vl: list val) rest R :
  writable_share sh -> Zlength vl = 16 ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (upd_Znth 11 vl (Vint (Int.repr (-1521486534)))) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert rest R ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (vl) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert (Ssequence b2s_iv_st11 rest) R.
Proof.
intros SH Hl Hrest.
unfold b2s_iv_st11. simpl. abbreviate_semax.
repeat forward.
eapply semax_pre; [ | exact Hrest ].
generalize (upd_Znth 11 vl (Vint (Int.repr (-1521486534)))); intro vv.
entailer!.
Qed.

Lemma b2s_iv5_st12_ok {Espec: OracleKind} sh ctx f0 dsh data n bs gv v_m v_v tt hk mw dp nb ic (vl: list val) rest R :
  writable_share sh -> Zlength vl = 16 ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (upd_Znth 12 vl (Vint (Int.xor (Int.repr 1359893119) (b2s_t0 tt)))) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert rest R ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (vl) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert (Ssequence b2s_iv_st12 rest) R.
Proof.
intros SH Hl Hrest.
unfold b2s_iv_st12. simpl. abbreviate_semax.
repeat forward.
eapply semax_pre; [ | exact Hrest ].
generalize (upd_Znth 12 vl (Vint (Int.xor (Int.repr 1359893119) (b2s_t0 tt)))); intro vv.
entailer!.
Qed.

Lemma b2s_iv5_st13_ok {Espec: OracleKind} sh ctx f0 dsh data n bs gv v_m v_v tt hk mw dp nb ic (vl: list val) rest R :
  writable_share sh -> Zlength vl = 16 ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (upd_Znth 13 vl (Vint (Int.xor (Int.repr (-1694144372)) (b2s_t1 tt)))) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert rest R ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (vl) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert (Ssequence b2s_iv_st13 rest) R.
Proof.
intros SH Hl Hrest.
unfold b2s_iv_st13. simpl. abbreviate_semax.
repeat forward.
eapply semax_pre; [ | exact Hrest ].
generalize (upd_Znth 13 vl (Vint (Int.xor (Int.repr (-1694144372)) (b2s_t1 tt)))); intro vv.
entailer!.
Qed.

Lemma b2s_iv5_st14_ok {Espec: OracleKind} sh ctx f0 dsh data n bs gv v_m v_v tt hk mw dp nb ic (vl: list val) rest R :
  writable_share sh -> Zlength vl = 16 ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (upd_Znth 14 vl (Vint (Int.xor (Int.repr 528734635) f0))) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert rest R ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (vl) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert (Ssequence b2s_iv_st14 rest) R.
Proof.
intros SH Hl Hrest.
unfold b2s_iv_st14. simpl. abbreviate_semax.
repeat forward.
eapply semax_pre; [ | exact Hrest ].
generalize (upd_Znth 14 vl (Vint (Int.xor (Int.repr 528734635) f0))); intro vv.
entailer!.
Qed.

Lemma b2s_iv5_st15_ok {Espec: OracleKind} sh ctx f0 dsh data n bs gv v_m v_v tt hk mw dp nb ic (vl: list val) rest R :
  writable_share sh -> Zlength vl = 16 ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (upd_Znth 15 vl (Vint (Int.xor (Int.repr 1541459225) Int.zero))) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert rest R ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (vl) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert (Ssequence b2s_iv_st15 rest) R.
Proof.
intros SH Hl Hrest.
unfold b2s_iv_st15. simpl. abbreviate_semax.
repeat forward.
eapply semax_pre; [ | exact Hrest ].
generalize (upd_Znth 15 vl (Vint (Int.xor (Int.repr 1541459225) Int.zero))); intro vv.
entailer!.
Qed.

Lemma b2s_iv5_ok {Espec: OracleKind} sh ctx f0 dsh data n bs gv v_m v_v tt hk mw dp nb ic (vl: list val) rest R :
  writable_share sh -> Zlength vl = 16 ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (upd_Znth 15 (upd_Znth 14 (upd_Znth 13 (upd_Znth 12 (upd_Znth 11 (upd_Znth 10 (upd_Znth 9 (upd_Znth 8 (vl) (Vint (Int.repr 1779033703))) (Vint (Int.repr (-1150833019)))) (Vint (Int.repr 1013904242))) (Vint (Int.repr (-1521486534)))) (Vint (Int.xor (Int.repr 1359893119) (b2s_t0 tt)))) (Vint (Int.xor (Int.repr (-1694144372)) (b2s_t1 tt)))) (Vint (Int.xor (Int.repr 528734635) f0))) (Vint (Int.xor (Int.repr 1541459225) Int.zero))) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert rest R ->
  semax b2s_cDelta5 (PROP () LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
         temp code._ctx ctx; temp code._data dp; temp code._nblocks nb; temp code._inc ic)
     SEP (data_at Tsh (tarray tuint 16) (vl) v_v;
       data_at Tsh (tarray tuint 16) (map Vint mw) v_m; blake2s_globals gv;
       field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 tt); Vint (b2s_t1 tt)] ctx;
       field_at sh t_blake2s_ctx (DOT _h) (map Vint hk) ctx;
       field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
       data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert (b2s_iv rest) R.
Proof.
intros SH Hl Hrest.
change (b2s_iv rest) with
  (Ssequence b2s_iv_st8 (Ssequence b2s_iv_st9 (Ssequence b2s_iv_st10 (Ssequence b2s_iv_st11
  (Ssequence b2s_iv_st12 (Ssequence b2s_iv_st13 (Ssequence b2s_iv_st14 (Ssequence b2s_iv_st15 rest)))))))).
apply b2s_iv5_st8_ok; [auto | rewrite ?Zlength_upd_Znth; auto | ].
apply b2s_iv5_st9_ok; [auto | rewrite ?Zlength_upd_Znth; auto | ].
apply b2s_iv5_st10_ok; [auto | rewrite ?Zlength_upd_Znth; auto | ].
apply b2s_iv5_st11_ok; [auto | rewrite ?Zlength_upd_Znth; auto | ].
apply b2s_iv5_st12_ok; [auto | rewrite ?Zlength_upd_Znth; auto | ].
apply b2s_iv5_st13_ok; [auto | rewrite ?Zlength_upd_Znth; auto | ].
apply b2s_iv5_st14_ok; [auto | rewrite ?Zlength_upd_Znth; auto | ].
apply b2s_iv5_st15_ok; [auto | rewrite ?Zlength_upd_Znth; auto | ].
exact Hrest.
Qed.
